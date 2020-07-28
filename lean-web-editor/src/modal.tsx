import React from 'react';
import { ModalContent } from './modal-content';

interface ModalState {
  isOpen: boolean;
}

// https://assortment.io/posts/accessible-modal-component-react-portals-part-1 & 2
// TODO: change focus back to button when modal closes
export class Modal extends React.Component<{}, ModalState> {
  private modalNode: Node;
  constructor(props) {
    super(props);
    this.state = {
      isOpen: false,
    };
    this.open = this.open.bind(this);
    this.close = this.close.bind(this);
    this.keyDown = this.keyDown.bind(this);
    this.clickAway = this.clickAway.bind(this);
  }

  open() {
    this.setState({ isOpen: true }, () => {});
  }
  close() {
    this.setState({ isOpen: false });
  }
  keyDown({ keyCode }) {
    return keyCode === 27 && this.close();
  }
  clickAway(e) {
    if (this.modalNode && this.modalNode.contains(e.target)) {
      return;
    }
    this.close();
  }

  render() {
    return (
      <React.Fragment>
        <button className='modalButton' onClick={this.open}>
          ?
        </button>
        {this.state.isOpen && (
          <ModalContent
            onClose={this.close}
            onKeyDown={this.keyDown}
            clickAway={this.clickAway}
            modalRef={(n) => (this.modalNode = n)}
          />
        )}
      </React.Fragment>
    );
  }
}
